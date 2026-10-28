import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10184 = true := by
  decide +kernel

theorem tot10184 : totK PD2M8K2 D2M8K2.t10184 = [0, 0, 166756909574, 459091131347, 265064290189, 22787847221, 0, 0] := by
  decide +kernel

theorem rows10185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10185 = true := by
  decide +kernel

theorem tot10185 : totK PD2M8K2 D2M8K2.t10185 = [0, 0, 159687206009, 431860827742, 282324363318, 29109532115, 0, 0] := by
  decide +kernel

theorem rows10186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10186 = true := by
  decide +kernel

theorem tot10186 : totK PD2M8K2 D2M8K2.t10186 = [0, 0, 89188854363, 360091706552, 369049269231, 64629536003, 1107157161, 0] := by
  decide +kernel

theorem rows10187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10187 = true := by
  decide +kernel

theorem tot10187 : totK PD2M8K2 D2M8K2.t10187 = [0, 0, 0, 292695378890, 471001759272, 110471134633, 3824247485, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
