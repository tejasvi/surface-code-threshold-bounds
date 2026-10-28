import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5672 = true := by
  decide +kernel

theorem tot5672 : totK PD2M8K2 D2M8K2.t5672 = [0, 0, 207207532479, 473573099144, 172514650775, 7182288656, 0, 0] := by
  decide +kernel

theorem rows5673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5673 = true := by
  decide +kernel

theorem tot5673 : totK PD2M8K2 D2M8K2.t5673 = [0, 179733180668, 391514607406, 208220663807, 104586873092, 13326740810, 0, 0] := by
  decide +kernel

theorem rows5674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5674 = true := by
  decide +kernel

theorem tot5674 : totK PD2M8K2 D2M8K2.t5674 = [0, 173442067471, 463424045347, 237267229469, 17044607505, 0, 0, 0] := by
  decide +kernel

theorem rows5675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5675 = true := by
  decide +kernel

theorem tot5675 : totK PD2M8K2 D2M8K2.t5675 = [0, 88237066013, 360966575789, 372375981397, 78120966028, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
