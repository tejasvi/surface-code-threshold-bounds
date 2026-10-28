import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7100 = true := by
  decide +kernel

theorem tot7100 : totK PD2M8K2 D2M8K2.t7100 = [0, 62729537426, 326427582189, 408537187955, 95564560666, 1268739303, 0, 0] := by
  decide +kernel

theorem rows7101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7101 = true := by
  decide +kernel

theorem tot7101 : totK PD2M8K2 D2M8K2.t7101 = [0, 0, 227713312300, 496555161877, 160853785015, 4763850746, 0, 0] := by
  decide +kernel

theorem rows7102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7102 = true := by
  decide +kernel

theorem tot7102 : totK PD2M8K2 D2M8K2.t7102 = [0, 0, 183421711747, 477470627946, 219234570034, 12886858747, 0, 0] := by
  decide +kernel

theorem rows7103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7103 = true := by
  decide +kernel

theorem tot7103 : totK PD2M8K2 D2M8K2.t7103 = [0, 0, 209168880443, 470740458367, 187076041909, 9653832318, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
