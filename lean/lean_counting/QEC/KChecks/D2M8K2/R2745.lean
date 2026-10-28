import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10980 = true := by
  decide +kernel

theorem tot10980 : totK PD2M8K2 D2M8K2.t10980 = [0, 171846236062, 465242946721, 247451109063, 14822326375, 0, 0, 0] := by
  decide +kernel

theorem rows10981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10981 = true := by
  decide +kernel

theorem tot10981 : totK PD2M8K2 D2M8K2.t10981 = [125231109916, 351135190713, 304757736690, 121128680749, 6982338906, 0, 0, 0] := by
  decide +kernel

theorem rows10982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10982 = true := by
  decide +kernel

theorem tot10982 : totK PD2M8K2 D2M8K2.t10982 = [170885816894, 447836779709, 269811162959, 28157958200, 0, 0, 0, 0] := by
  decide +kernel

theorem rows10983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10983 = true := by
  decide +kernel

theorem tot10983 : totK PD2M8K2 D2M8K2.t10983 = [137386574906, 440074498624, 290515331913, 24699592767, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
