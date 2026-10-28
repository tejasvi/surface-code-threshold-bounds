import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8844 = true := by
  decide +kernel

theorem tot8844 : totK PD2M8K2 D2M8K2.t8844 = [87346212865, 331266245058, 395868028907, 86509613708, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows8845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8845 = true := by
  decide +kernel

theorem tot8845 : totK PD2M8K2 D2M8K2.t8845 = [0, 229845712055, 478454692557, 168469977830, 9482920370, 0, 0, 0] := by
  decide +kernel

theorem rows8846 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8846 = true := by
  decide +kernel

theorem tot8846 : totK PD2M8K2 D2M8K2.t8846 = [151299149447, 394630678322, 287050093571, 63257263055, 2569691499, 0, 0, 0] := by
  decide +kernel

theorem rows8847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8847 = true := by
  decide +kernel

theorem tot8847 : totK PD2M8K2 D2M8K2.t8847 = [166429125923, 433489232192, 255206961917, 26929678957, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
