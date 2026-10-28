import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7240 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7240 = true := by
  decide +kernel

theorem tot7240 : totK PA10K2 A10K2.t7240 = [0, 240820552821, 1054524775708, 1857766709813, 1393789258996, 294058632567, 10719219105, 0, 0, 0] := by
  decide +kernel

theorem rows7241 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7241 = true := by
  decide +kernel

theorem tot7241 : totK PA10K2 A10K2.t7241 = [0, 433044328481, 1830175580197, 2208185977991, 676968897027, 32370737181, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7242 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7242 = true := by
  decide +kernel

theorem tot7242 : totK PA10K2 A10K2.t7242 = [0, 0, 683725275708, 2145979253320, 1838908278952, 398102399462, 18609374344, 0, 0, 0] := by
  decide +kernel

theorem rows7243 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7243 = true := by
  decide +kernel

theorem tot7243 : totK PA10K2 A10K2.t7243 = [0, 552204907645, 1838893205121, 1856613201508, 681802120347, 67316623566, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
