import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1068 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1068 = true := by
  decide +kernel

theorem tot1068 : totK PA10K2 A10K2.t1068 = [0, 0, 110665848719, 778248927849, 1870189327378, 1539761731316, 352749157048, 12477124820, 0, 0] := by
  decide +kernel

theorem rows1069 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1069 = true := by
  decide +kernel

theorem tot1069 : totK PA10K2 A10K2.t1069 = [0, 0, 365700740725, 1632250969517, 2045961883141, 682339604112, 52178729445, 0, 0, 0] := by
  decide +kernel

theorem rows1070 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1070 = true := by
  decide +kernel

theorem tot1070 : totK PA10K2 A10K2.t1070 = [0, 0, 423228750236, 1622742449594, 2028893560355, 738965422540, 47276256389, 0, 0, 0] := by
  decide +kernel

theorem rows1071 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1071 = true := by
  decide +kernel

theorem tot1071 : totK PA10K2 A10K2.t1071 = [0, 77065070666, 501626707277, 1696058218717, 2100611159054, 757609591420, 57551169768, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
