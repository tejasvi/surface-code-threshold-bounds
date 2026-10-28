import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4992 = true := by
  decide +kernel

theorem tot4992 : totK PD2M8K2 D2M8K2.t4992 = [0, 0, 49108726173, 390842374245, 424574254007, 54797446152, 0, 0] := by
  decide +kernel

theorem rows4993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4993 = true := by
  decide +kernel

theorem tot4993 : totK PD2M8K2 D2M8K2.t4993 = [0, 0, 33969887456, 226345218682, 455822781986, 156170593142, 5218872685, 0] := by
  decide +kernel

theorem rows4994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4994 = true := by
  decide +kernel

theorem tot4994 : totK PD2M8K2 D2M8K2.t4994 = [0, 0, 197100682017, 453203310841, 240084078198, 23043327343, 0, 0] := by
  decide +kernel

theorem rows4995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4995 = true := by
  decide +kernel

theorem tot4995 : totK PD2M8K2 D2M8K2.t4995 = [0, 0, 180322658724, 456396293641, 238391345475, 16972201627, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
