import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7088 = true := by
  decide +kernel

theorem tot7088 : totK PD2M8K2 D2M8K2.t7088 = [0, 0, 278551077894, 461936657704, 174930288646, 15054179382, 0, 0] := by
  decide +kernel

theorem rows7089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7089 = true := by
  decide +kernel

theorem tot7089 : totK PD2M8K2 D2M8K2.t7089 = [0, 0, 167340113675, 491919604957, 225923634535, 6568891087, 0, 0] := by
  decide +kernel

theorem rows7090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7090 = true := by
  decide +kernel

theorem tot7090 : totK PD2M8K2 D2M8K2.t7090 = [0, 172437555119, 441814601795, 255447816980, 48383417076, 3060566153, 0, 0] := by
  decide +kernel

theorem rows7091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7091 = true := by
  decide +kernel

theorem tot7091 : totK PD2M8K2 D2M8K2.t7091 = [0, 193923009753, 476003115189, 222577033176, 12373752831, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
