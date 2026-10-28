import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5860 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5860 = true := by
  decide +kernel

theorem tot5860 : totK PA10K2 A10K2.t5860 = [0, 0, 0, 236081878322, 1013214520287, 1898500747944, 1229381147923, 201143425607, 6121173289, 0] := by
  decide +kernel

theorem rows5861 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5861 = true := by
  decide +kernel

theorem tot5861 : totK PA10K2 A10K2.t5861 = [0, 0, 286479695196, 1193846178001, 1928033226810, 1211509654005, 190298179986, 15154228141, 0, 0] := by
  decide +kernel

theorem rows5862 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5862 = true := by
  decide +kernel

theorem tot5862 : totK PA10K2 A10K2.t5862 = [0, 0, 446546377714, 1778201408963, 1953878376258, 550697079995, 24433330952, 0, 0, 0] := by
  decide +kernel

theorem rows5863 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5863 = true := by
  decide +kernel

theorem tot5863 : totK PA10K2 A10K2.t5863 = [0, 0, 0, 456496623551, 1875506422020, 1824172811800, 399200557411, 25371180993, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
