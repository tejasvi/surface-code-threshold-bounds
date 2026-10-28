import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15160 = true := by
  decide +kernel

theorem tot15160 : totK PD2M8K2 D2M8K2.t15160 = [0, 0, 0, 247715951172, 478804741199, 147953715735, 5425831197, 0] := by
  decide +kernel

theorem rows15161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15161 = true := by
  decide +kernel

theorem tot15161 : totK PD2M8K2 D2M8K2.t15161 = [0, 0, 149917210474, 454047690014, 269388512057, 24553913284, 0, 0] := by
  decide +kernel

theorem rows15162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15162 = true := by
  decide +kernel

theorem tot15162 : totK PD2M8K2 D2M8K2.t15162 = [0, 0, 188356162331, 452319217793, 227634313993, 13925320504, 0, 0] := by
  decide +kernel

theorem rows15163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15163 = true := by
  decide +kernel

theorem tot15163 : totK PD2M8K2 D2M8K2.t15163 = [0, 0, 203887844521, 499247196585, 181529292052, 5242142951, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
