import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows156 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t156 = true := by
  decide +kernel

theorem tot156 : totK PA10K2 A10K2.t156 = [200454091944, 829519989511, 1575044088856, 1729694535043, 692850946906, 57551169768, 0, 0, 0, 0] := by
  decide +kernel

theorem rows157 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t157 = true := by
  decide +kernel

theorem tot157 : totK PA10K2 A10K2.t157 = [378776043699, 1676212367583, 2199684050303, 839652404600, 51528640634, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows158 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t158 = true := by
  decide +kernel

theorem tot158 : totK PA10K2 A10K2.t158 = [105088995274, 809463168523, 1971696221355, 1716371878757, 428385667938, 25734533292, 0, 0, 0, 0] := by
  decide +kernel

theorem rows159 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t159 = true := by
  decide +kernel

theorem tot159 : totK PA10K2 A10K2.t159 = [568424756401, 1982485503965, 1997418645050, 554783419694, 39064046553, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
