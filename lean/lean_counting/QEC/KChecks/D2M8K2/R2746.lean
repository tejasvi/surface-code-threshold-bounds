import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10984 = true := by
  decide +kernel

theorem tot10984 : totK PD2M8K2 D2M8K2.t10984 = [0, 211224310258, 493968962869, 179992848220, 9587713104, 0, 0, 0] := by
  decide +kernel

theorem rows10985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10985 = true := by
  decide +kernel

theorem tot10985 : totK PD2M8K2 D2M8K2.t10985 = [84862533686, 313211754815, 377227739527, 102769167119, 3462014130, 0, 0, 0] := by
  decide +kernel

theorem rows10986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10986 = true := by
  decide +kernel

theorem tot10986 : totK PD2M8K2 D2M8K2.t10986 = [168608804140, 459453488048, 264024595232, 22839827200, 0, 0, 0, 0] := by
  decide +kernel

theorem rows10987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10987 = true := by
  decide +kernel

theorem tot10987 : totK PD2M8K2 D2M8K2.t10987 = [158693293996, 455238801395, 258897091697, 19843009905, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
