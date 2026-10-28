import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7796 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7796 = true := by
  decide +kernel

theorem tot7796 : totK PA10K2 A10K2.t7796 = [0, 0, 306392981073, 1499763337853, 2244232124409, 949020394557, 69413026218, 0, 0, 0] := by
  decide +kernel

theorem rows7797 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7797 = true := by
  decide +kernel

theorem tot7797 : totK PA10K2 A10K2.t7797 = [0, 0, 286110476401, 1222186750764, 1954854229432, 1354778789098, 240091107184, 7047025452, 0, 0] := by
  decide +kernel

theorem rows7798 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7798 = true := by
  decide +kernel

theorem tot7798 : totK PA10K2 A10K2.t7798 = [0, 0, 581583812515, 1927456291401, 1876239542087, 529941843911, 23581316846, 0, 0, 0] := by
  decide +kernel

theorem rows7799 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7799 = true := by
  decide +kernel

theorem tot7799 : totK PA10K2 A10K2.t7799 = [0, 0, 0, 773538483909, 2227916043354, 1660886185628, 256555482123, 6066958478, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
