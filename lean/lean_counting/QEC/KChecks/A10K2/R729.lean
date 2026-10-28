import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2916 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2916 = true := by
  decide +kernel

theorem tot2916 : totK PA10K2 A10K2.t2916 = [398073020871, 1532365331760, 2031202182761, 893854213039, 86461734967, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2917 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2917 = true := by
  decide +kernel

theorem tot2917 : totK PA10K2 A10K2.t2917 = [371657160808, 1677464862965, 2151132686969, 814365682283, 73076698181, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2918 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2918 = true := by
  decide +kernel

theorem tot2918 : totK PA10K2 A10K2.t2918 = [0, 534008523443, 1921815957358, 1859606191232, 473910333205, 31450896759, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2919 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2919 = true := by
  decide +kernel

theorem tot2919 : totK PA10K2 A10K2.t2919 = [561117401612, 1856131294014, 1841710115239, 616270099350, 59947891416, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
