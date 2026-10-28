import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9816 = true := by
  decide +kernel

theorem tot9816 : totK PD2M8K2 D2M8K2.t9816 = [0, 0, 182745090692, 468952591742, 215919441135, 12183533023, 0, 0] := by
  decide +kernel

theorem rows9817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9817 = true := by
  decide +kernel

theorem tot9817 : totK PD2M8K2 D2M8K2.t9817 = [0, 0, 162651761789, 471187228726, 237437194347, 11537559849, 0, 0] := by
  decide +kernel

theorem rows9818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9818 = true := by
  decide +kernel

theorem tot9818 : totK PD2M8K2 D2M8K2.t9818 = [0, 0, 200779328109, 466928619042, 196584688018, 12064174497, 0, 0] := by
  decide +kernel

theorem rows9819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9819 = true := by
  decide +kernel

theorem tot9819 : totK PD2M8K2 D2M8K2.t9819 = [0, 0, 183948200449, 500334450101, 204011037068, 5241682743, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
