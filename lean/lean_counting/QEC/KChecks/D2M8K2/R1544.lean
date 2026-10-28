import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6176 = true := by
  decide +kernel

theorem tot6176 : totK PD2M8K2 D2M8K2.t6176 = [0, 171428844504, 470917158871, 253584014870, 12696520176, 0, 0, 0] := by
  decide +kernel

theorem rows6177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6177 = true := by
  decide +kernel

theorem tot6177 : totK PD2M8K2 D2M8K2.t6177 = [0, 88825966916, 375983976659, 367289608520, 81189500548, 10444649207, 0, 0] := by
  decide +kernel

theorem rows6178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6178 = true := by
  decide +kernel

theorem tot6178 : totK PD2M8K2 D2M8K2.t6178 = [0, 0, 170403545340, 450578084298, 248121458431, 17508088435, 0, 0] := by
  decide +kernel

theorem rows6179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6179 = true := by
  decide +kernel

theorem tot6179 : totK PD2M8K2 D2M8K2.t6179 = [0, 17755325808, 188108658027, 456556170508, 210433330683, 8969136212, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
