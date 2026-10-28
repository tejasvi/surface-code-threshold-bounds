import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1836 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1836 = true := by
  decide +kernel

theorem tot1836 : totK PA10K2 A10K2.t1836 = [0, 0, 348653493608, 1585944854378, 2051903069872, 646888204102, 38769339849, 0, 0, 0] := by
  decide +kernel

theorem rows1837 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1837 = true := by
  decide +kernel

theorem tot1837 : totK PA10K2 A10K2.t1837 = [0, 0, 296268317924, 1246301593735, 1913909322669, 1042877320852, 166212260397, 5546304973, 0, 0] := by
  decide +kernel

theorem rows1838 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1838 = true := by
  decide +kernel

theorem tot1838 : totK PA10K2 A10K2.t1838 = [0, 0, 501233137592, 1907535814358, 2071421264443, 567248070274, 33869179644, 0, 0, 0] := by
  decide +kernel

theorem rows1839 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1839 = true := by
  decide +kernel

theorem tot1839 : totK PA10K2 A10K2.t1839 = [0, 506452765222, 1610669791421, 1624247527261, 793558163668, 350417788897, 43709387373, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
