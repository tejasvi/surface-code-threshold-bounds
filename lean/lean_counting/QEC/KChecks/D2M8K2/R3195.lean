import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12780 = true := by
  decide +kernel

theorem tot12780 : totK PD2M8K2 D2M8K2.t12780 = [0, 0, 197147718218, 471886858438, 228613004019, 16104584588, 0, 0] := by
  decide +kernel

theorem rows12781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12781 = true := by
  decide +kernel

theorem tot12781 : totK PD2M8K2 D2M8K2.t12781 = [0, 0, 185164566436, 477247905403, 217798635266, 12183533023, 0, 0] := by
  decide +kernel

theorem rows12782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12782 = true := by
  decide +kernel

theorem tot12782 : totK PD2M8K2 D2M8K2.t12782 = [0, 0, 30011752942, 327767632453, 429325102433, 84972737075, 1162935789, 0] := by
  decide +kernel

theorem rows12783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12783 = true := by
  decide +kernel

theorem tot12783 : totK PD2M8K2 D2M8K2.t12783 = [0, 0, 0, 198041105018, 447496476825, 185708145853, 11853261585, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
