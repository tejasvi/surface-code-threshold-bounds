import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6956 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6956 = true := by
  decide +kernel

theorem tot6956 : totK PA10K2 A10K2.t6956 = [0, 277894402602, 1233264558191, 1922620355836, 1240117950996, 208821383531, 5809256573, 0, 0, 0] := by
  decide +kernel

theorem rows6957 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6957 = true := by
  decide +kernel

theorem tot6957 : totK PA10K2 A10K2.t6957 = [0, 283322952595, 1469772677504, 2167682898313, 843725938341, 60211199503, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6958 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6958 = true := by
  decide +kernel

theorem tot6958 : totK PA10K2 A10K2.t6958 = [0, 0, 586743729225, 2003039767799, 1759030729327, 399429684503, 21557248062, 0, 0, 0] := by
  decide +kernel

theorem rows6959 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6959 = true := by
  decide +kernel

theorem tot6959 : totK PA10K2 A10K2.t6959 = [0, 0, 457261372542, 1815223889587, 2065458107732, 537922650430, 24141511674, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
