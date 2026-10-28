import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12148 = true := by
  decide +kernel

theorem tot12148 : totK PD2M8K2 D2M8K2.t12148 = [0, 0, 214334404133, 482912520688, 173285474008, 5013205623, 0, 0] := by
  decide +kernel

theorem rows12149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12149 = true := by
  decide +kernel

theorem tot12149 : totK PD2M8K2 D2M8K2.t12149 = [0, 0, 180457717811, 464447632848, 213548185399, 14222515117, 0, 0] := by
  decide +kernel

theorem rows12150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12150 = true := by
  decide +kernel

theorem tot12150 : totK PD2M8K2 D2M8K2.t12150 = [0, 0, 92049777499, 380790678412, 328126281909, 50775921898, 1095107716, 0] := by
  decide +kernel

theorem rows12151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12151 = true := by
  decide +kernel

theorem tot12151 : totK PD2M8K2 D2M8K2.t12151 = [0, 0, 0, 327557118605, 445322473651, 74760249352, 1067409660, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
