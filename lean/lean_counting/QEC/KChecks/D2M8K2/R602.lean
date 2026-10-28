import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2408 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2408 = true := by
  decide +kernel

theorem tot2408 : totK PD2M8K2 D2M8K2.t2408 = [0, 0, 298841964224, 495469879967, 99252473564, 1164319620, 0, 0] := by
  decide +kernel

theorem rows2409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2409 = true := by
  decide +kernel

theorem tot2409 : totK PD2M8K2 D2M8K2.t2409 = [0, 0, 216769432447, 481062799050, 174255432455, 7648099296, 0, 0] := by
  decide +kernel

theorem rows2410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2410 = true := by
  decide +kernel

theorem tot2410 : totK PD2M8K2 D2M8K2.t2410 = [0, 175090026286, 440229094034, 256971108601, 28430201062, 0, 0, 0] := by
  decide +kernel

theorem rows2411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2411 = true := by
  decide +kernel

theorem tot2411 : totK PD2M8K2 D2M8K2.t2411 = [0, 206157743362, 466216159121, 213111096790, 12438552724, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
