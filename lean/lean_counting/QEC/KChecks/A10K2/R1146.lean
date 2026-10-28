import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4584 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4584 = true := by
  decide +kernel

theorem tot4584 : totK PA10K2 A10K2.t4584 = [0, 0, 466201711566, 1913269702732, 1834412807237, 388808017600, 24969229125, 0, 0, 0] := by
  decide +kernel

theorem rows4585 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4585 = true := by
  decide +kernel

theorem tot4585 : totK PA10K2 A10K2.t4585 = [0, 489656864186, 1674840725699, 1801426857710, 659924477097, 103101992492, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows4586 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4586 = true := by
  decide +kernel

theorem tot4586 : totK PA10K2 A10K2.t4586 = [0, 334120399620, 1641757371135, 2066272431167, 640269070060, 47682698843, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4587 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4587 = true := by
  decide +kernel

theorem tot4587 : totK PA10K2 A10K2.t4587 = [0, 0, 727091950525, 2246873537649, 1479440402088, 167571562385, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
