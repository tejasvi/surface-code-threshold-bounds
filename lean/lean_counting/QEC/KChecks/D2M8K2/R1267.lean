import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5068 = true := by
  decide +kernel

theorem tot5068 : totK PD2M8K2 D2M8K2.t5068 = [0, 0, 17671726862, 291015268607, 450090878963, 99984612465, 3667207281, 0] := by
  decide +kernel

theorem rows5069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5069 = true := by
  decide +kernel

theorem tot5069 : totK PD2M8K2 D2M8K2.t5069 = [0, 0, 204461313613, 463216681532, 232111098383, 20847945325, 0, 0] := by
  decide +kernel

theorem rows5070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5070 = true := by
  decide +kernel

theorem tot5070 : totK PD2M8K2 D2M8K2.t5070 = [0, 73275311424, 215612982608, 367092826846, 238492049082, 20624007072, 0, 0] := by
  decide +kernel

theorem rows5071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5071 = true := by
  decide +kernel

theorem tot5071 : totK PD2M8K2 D2M8K2.t5071 = [0, 184457667684, 468451354476, 210677870936, 9852138406, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
