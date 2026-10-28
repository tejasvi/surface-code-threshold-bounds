import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3188 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3188 = true := by
  decide +kernel

theorem tot3188 : totK PA10K2 A10K2.t3188 = [0, 0, 360666413497, 1237331004640, 1800885611692, 1065936045399, 178995699509, 5517381808, 0, 0] := by
  decide +kernel

theorem rows3189 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3189 = true := by
  decide +kernel

theorem tot3189 : totK PA10K2 A10K2.t3189 = [0, 0, 361708485942, 1718867900456, 2014546850444, 573402709781, 32877822373, 0, 0, 0] := by
  decide +kernel

theorem rows3190 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3190 = true := by
  decide +kernel

theorem tot3190 : totK PA10K2 A10K2.t3190 = [0, 0, 66962646299, 723701029138, 2069971896337, 1423199487580, 212986111769, 6121173289, 0, 0] := by
  decide +kernel

theorem rows3191 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3191 = true := by
  decide +kernel

theorem tot3191 : totK PA10K2 A10K2.t3191 = [0, 0, 530421714505, 1941407066136, 1993640071891, 545514092543, 25852139541, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
