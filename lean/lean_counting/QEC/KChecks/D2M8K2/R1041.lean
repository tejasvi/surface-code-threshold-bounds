import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4164 = true := by
  decide +kernel

theorem tot4164 : totK PD2M8K2 D2M8K2.t4164 = [0, 162975290697, 480218766764, 263008737550, 14773923819, 0, 0, 0] := by
  decide +kernel

theorem rows4165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4165 = true := by
  decide +kernel

theorem tot4165 : totK PD2M8K2 D2M8K2.t4165 = [0, 0, 203677390264, 466478936642, 222818382521, 21391863750, 0, 0] := by
  decide +kernel

theorem rows4166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4166 = true := by
  decide +kernel

theorem tot4166 : totK PD2M8K2 D2M8K2.t4166 = [0, 0, 189547242245, 470402282661, 225197142236, 9392638393, 0, 0] := by
  decide +kernel

theorem rows4167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4167 = true := by
  decide +kernel

theorem tot4167 : totK PD2M8K2 D2M8K2.t4167 = [0, 146733090398, 347934385204, 286482131653, 115333234922, 6804944647, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
