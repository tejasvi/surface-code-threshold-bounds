import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14324 = true := by
  decide +kernel

theorem tot14324 : totK PD2M8K2 D2M8K2.t14324 = [0, 170148724552, 465055950988, 253204695719, 13705139214, 0, 0, 0] := by
  decide +kernel

theorem rows14325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14325 = true := by
  decide +kernel

theorem tot14325 : totK PD2M8K2 D2M8K2.t14325 = [0, 88995923185, 384455286565, 360300614658, 76242890534, 10444649207, 0, 0] := by
  decide +kernel

theorem rows14326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14326 = true := by
  decide +kernel

theorem tot14326 : totK PD2M8K2 D2M8K2.t14326 = [0, 0, 172290683253, 463433865064, 253916722007, 14929139160, 0, 0] := by
  decide +kernel

theorem rows14327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14327 = true := by
  decide +kernel

theorem tot14327 : totK PD2M8K2 D2M8K2.t14327 = [0, 0, 174063355255, 470790929012, 227301540518, 9951216795, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
