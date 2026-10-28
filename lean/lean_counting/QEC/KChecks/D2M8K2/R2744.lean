import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10976 = true := by
  decide +kernel

theorem tot10976 : totK PD2M8K2 D2M8K2.t10976 = [34892481028, 311916632262, 443338237135, 98784932688, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows10977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10977 = true := by
  decide +kernel

theorem tot10977 : totK PD2M8K2 D2M8K2.t10977 = [71554482467, 355715067917, 423768808133, 54573248362, 0, 0, 0, 0] := by
  decide +kernel

theorem rows10978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10978 = true := by
  decide +kernel

theorem tot10978 : totK PD2M8K2 D2M8K2.t10978 = [167523605619, 441113559540, 279851521869, 30359669792, 0, 0, 0, 0] := by
  decide +kernel

theorem rows10979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10979 = true := by
  decide +kernel

theorem tot10979 : totK PD2M8K2 D2M8K2.t10979 = [88090392500, 394884166115, 350343121972, 72866177625, 10438989511, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
