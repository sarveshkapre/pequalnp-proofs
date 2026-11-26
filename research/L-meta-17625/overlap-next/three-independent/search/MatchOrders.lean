import Mathlib.Data.Fintype.Pi
import MatchWindow

namespace MatchProjected

theorem six_orders : ∀ o : Fin 4 → Bool, (List.ofFn o).count true = 2 →
    o = ![false,false,true,true] ∨
    o = ![false,true,false,true] ∨
    o = ![false,true,true,false] ∨
    o = ![true,false,false,true] ∨
    o = ![true,false,true,false] ∨
    o = ![true,true,false,false] := by decide

end MatchProjected
