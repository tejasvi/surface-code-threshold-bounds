import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7504 = true := by
  decide +kernel

theorem tot7504 : totK PD2M8K2 D2M8K2.t7504 = [0, 0, 204146525529, 473701557912, 185296081155, 7619554618, 0, 0] := by
  decide +kernel

theorem rows7505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7505 = true := by
  decide +kernel

theorem tot7505 : totK PD2M8K2 D2M8K2.t7505 = [0, 0, 175556421138, 492130589079, 230776847500, 6810167373, 0, 0] := by
  decide +kernel

theorem rows7506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7506 = true := by
  decide +kernel

theorem tot7506 : totK PD2M8K2 D2M8K2.t7506 = [0, 0, 169191171560, 465710692611, 242853444404, 11610990151, 0, 0] := by
  decide +kernel

theorem rows7507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7507 = true := by
  decide +kernel

theorem tot7507 : totK PD2M8K2 D2M8K2.t7507 = [0, 183243395725, 453237686241, 264036344537, 31878786398, 3947401329, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
