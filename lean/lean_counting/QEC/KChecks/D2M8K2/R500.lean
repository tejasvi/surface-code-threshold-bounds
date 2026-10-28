import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2000 = true := by
  decide +kernel

theorem tot2000 : totK PD2M8K2 D2M8K2.t2000 = [0, 0, 173526222618, 461204031403, 262062423483, 22742514249, 0, 0] := by
  decide +kernel

theorem rows2001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2001 = true := by
  decide +kernel

theorem tot2001 : totK PD2M8K2 D2M8K2.t2001 = [0, 0, 178800725029, 468299127473, 246354884725, 13525750331, 0, 0] := by
  decide +kernel

theorem rows2002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2002 = true := by
  decide +kernel

theorem tot2002 : totK PD2M8K2 D2M8K2.t2002 = [0, 179275612758, 428706073665, 207589998359, 63112251319, 9718976469, 0, 0] := by
  decide +kernel

theorem rows2003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2003 = true := by
  decide +kernel

theorem tot2003 : totK PD2M8K2 D2M8K2.t2003 = [0, 191126525948, 472048739246, 226572766662, 12534051746, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
