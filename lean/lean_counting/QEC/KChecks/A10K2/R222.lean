import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows888 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t888 = true := by
  decide +kernel

theorem tot888 : totK PA10K2 A10K2.t888 = [0, 468370069426, 1813877618082, 2029151339084, 594655408972, 23556948391, 0, 0, 0, 0] := by
  decide +kernel

theorem rows889 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t889 = true := by
  decide +kernel

theorem tot889 : totK PA10K2 A10K2.t889 = [0, 0, 688251295968, 2188645427050, 1652223057610, 283870979741, 6904928264, 0, 0, 0] := by
  decide +kernel

theorem rows890 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t890 = true := by
  decide +kernel

theorem tot890 : totK PA10K2 A10K2.t890 = [0, 420068636232, 1645646510230, 1911392199268, 673834589098, 63857643621, 0, 0, 0, 0] := by
  decide +kernel

theorem rows891 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t891 = true := by
  decide +kernel

theorem tot891 : totK PA10K2 A10K2.t891 = [0, 308336809981, 1423616359421, 2125316762620, 1047491327909, 104364424953, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
