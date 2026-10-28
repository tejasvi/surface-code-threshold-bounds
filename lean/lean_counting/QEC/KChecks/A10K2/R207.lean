import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows828 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t828 = true := by
  decide +kernel

theorem tot828 : totK PA10K2 A10K2.t828 = [0, 0, 605644445534, 2090958882996, 1936705365459, 343579759412, 6157148557, 0, 0, 0] := by
  decide +kernel

theorem rows829 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t829 = true := by
  decide +kernel

theorem tot829 : totK PA10K2 A10K2.t829 = [0, 426991113182, 1346024400441, 1547653342928, 1051465473263, 451050916943, 48886019071, 0, 0, 0] := by
  decide +kernel

theorem rows830 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t830 = true := by
  decide +kernel

theorem tot830 : totK PA10K2 A10K2.t830 = [0, 419880263964, 1751664780549, 2068022246773, 672716856481, 22226675995, 0, 0, 0, 0] := by
  decide +kernel

theorem rows831 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t831 = true := by
  decide +kernel

theorem tot831 : totK PA10K2 A10K2.t831 = [0, 0, 550988780261, 1923013418962, 1806823667636, 436368383267, 25734533292, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
