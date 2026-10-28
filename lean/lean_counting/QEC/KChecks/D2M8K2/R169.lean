import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows676 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t676 = true := by
  decide +kernel

theorem tot676 : totK PD2M8K2 D2M8K2.t676 = [0, 92162477754, 395844446803, 371151486562, 43549867300, 0, 0, 0] := by
  decide +kernel

theorem rows677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t677 = true := by
  decide +kernel

theorem tot677 : totK PD2M8K2 D2M8K2.t677 = [0, 167101610685, 447305782040, 272111333266, 21021880940, 0, 0, 0] := by
  decide +kernel

theorem rows678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t678 = true := by
  decide +kernel

theorem tot678 : totK PD2M8K2 D2M8K2.t678 = [0, 188754977902, 464694882447, 222008976247, 14231324056, 0, 0, 0] := by
  decide +kernel

theorem rows679 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t679 = true := by
  decide +kernel

theorem tot679 : totK PD2M8K2 D2M8K2.t679 = [0, 184737667231, 464289488780, 244453317234, 19920018668, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
