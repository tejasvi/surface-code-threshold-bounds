import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7176 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7176 = true := by
  decide +kernel

theorem tot7176 : totK PA10K2 A10K2.t7176 = [0, 0, 174394568313, 914373507819, 1864163241416, 1385969510662, 291051799642, 10589884120, 0, 0] := by
  decide +kernel

theorem rows7177 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7177 = true := by
  decide +kernel

theorem tot7177 : totK PA10K2 A10K2.t7177 = [0, 0, 514051482079, 1809318006791, 1868968604722, 519610758120, 31608797364, 0, 0, 0] := by
  decide +kernel

theorem rows7178 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7178 = true := by
  decide +kernel

theorem tot7178 : totK PA10K2 A10K2.t7178 = [0, 0, 46585974599, 1203149055492, 2350875074261, 980762130347, 71239518531, 0, 0, 0] := by
  decide +kernel

theorem rows7179 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7179 = true := by
  decide +kernel

theorem tot7179 : totK PA10K2 A10K2.t7179 = [0, 0, 495776073559, 1606436837215, 1816491064871, 838010016205, 147938853711, 5546304973, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
