// data / seeds
// FiniteFlatCover 16.0.1 -- load with AttachSpec("spec").
import "seed_difference.m": FFCSeedDifference;
import "seed_distinct.m": FFCSeedDistinct;
import "seed_square_diagonal.m": FFCSeedSquareDiagonal;
import "seed_square_other.m": FFCSeedSquareOther;

function FFCResolventSeedTerms(which)
    case which:
        when 1: return FFCSeedDistinct;
        when 2: return FFCSeedSquareOther;
        when 3: return FFCSeedDifference;
        when 4: return FFCSeedSquareDiagonal;
    else
        error "Unknown sextic seed";
    end case;
end function;
