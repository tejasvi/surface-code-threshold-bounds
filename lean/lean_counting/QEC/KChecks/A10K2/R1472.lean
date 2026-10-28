import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5888 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5888 = true := by
  decide +kernel

theorem tot5888 : totK PA10K2 A10K2.t5888 = [0, 0, 0, 444597179661, 1758798677157, 2000128236117, 522016992053, 18129294114, 0, 0] := by
  decide +kernel

theorem rows5889 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5889 = true := by
  decide +kernel

theorem tot5889 : totK PA10K2 A10K2.t5889 = [0, 0, 0, 0, 494118611301, 1812939533952, 1693864533559, 429053472165, 30074883546, 0] := by
  decide +kernel

theorem rows5890 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5890 = true := by
  decide +kernel

theorem tot5890 : totK PA10K2 A10K2.t5890 = [0, 0, 0, 571001356634, 1859841978737, 1765716304938, 478557485680, 33765343118, 0, 0] := by
  decide +kernel

theorem rows5891 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5891 = true := by
  decide +kernel

theorem tot5891 : totK PA10K2 A10K2.t5891 = [0, 0, 0, 162979351478, 1095411170998, 2014101598754, 1109154623233, 229692028852, 19575605953, 0] := by
  decide +kernel

end QECKChecks.A10K2
