import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13312 = true := by
  decide +kernel

theorem tot13312 : totK PD2M8K2 D2M8K2.t13312 = [0, 0, 134420827091, 462767741836, 270363768484, 14869252888, 0, 0] := by
  decide +kernel

theorem rows13313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13313 = true := by
  decide +kernel

theorem tot13313 : totK PD2M8K2 D2M8K2.t13313 = [0, 0, 0, 217151509158, 474103108452, 160192927029, 9579374723, 0] := by
  decide +kernel

theorem rows13314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13314 = true := by
  decide +kernel

theorem tot13314 : totK PD2M8K2 D2M8K2.t13314 = [0, 0, 83655740246, 346912160684, 327275423772, 80945856324, 3436822651, 0] := by
  decide +kernel

theorem rows13315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13315 = true := by
  decide +kernel

theorem tot13315 : totK PD2M8K2 D2M8K2.t13315 = [0, 0, 189959856828, 459332308826, 245072106357, 18252358503, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
