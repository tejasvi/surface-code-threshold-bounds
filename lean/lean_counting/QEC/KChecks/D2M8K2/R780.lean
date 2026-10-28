import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3120 = true := by
  decide +kernel

theorem tot3120 : totK PD2M8K2 D2M8K2.t3120 = [0, 171765687307, 457980067200, 238270600089, 13964593734, 0, 0, 0] := by
  decide +kernel

theorem rows3121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3121 = true := by
  decide +kernel

theorem tot3121 : totK PD2M8K2 D2M8K2.t3121 = [0, 189320066150, 474762161564, 212158024207, 9757737807, 0, 0, 0] := by
  decide +kernel

theorem rows3122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3122 = true := by
  decide +kernel

theorem tot3122 : totK PD2M8K2 D2M8K2.t3122 = [0, 189673955271, 468680353466, 207534169241, 12403393969, 0, 0, 0] := by
  decide +kernel

theorem rows3123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3123 = true := by
  decide +kernel

theorem tot3123 : totK PD2M8K2 D2M8K2.t3123 = [0, 157241723419, 473948210162, 260450163449, 12280293419, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
