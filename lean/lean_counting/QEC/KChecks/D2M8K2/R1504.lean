import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6016 = true := by
  decide +kernel

theorem tot6016 : totK PD2M8K2 D2M8K2.t6016 = [0, 0, 239289251104, 495264764918, 150633022749, 2233847856, 0, 0] := by
  decide +kernel

theorem rows6017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6017 = true := by
  decide +kernel

theorem tot6017 : totK PD2M8K2 D2M8K2.t6017 = [0, 0, 164762100653, 452044591846, 271222090803, 28488717195, 0, 0] := by
  decide +kernel

theorem rows6018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6018 = true := by
  decide +kernel

theorem tot6018 : totK PD2M8K2 D2M8K2.t6018 = [0, 0, 183903537341, 485354192496, 216082839000, 6491593854, 0, 0] := by
  decide +kernel

theorem rows6019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6019 = true := by
  decide +kernel

theorem tot6019 : totK PD2M8K2 D2M8K2.t6019 = [0, 0, 170538721366, 453840950257, 248296277513, 21383138092, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
