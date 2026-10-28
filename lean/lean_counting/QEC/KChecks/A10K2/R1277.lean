import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5108 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5108 = true := by
  decide +kernel

theorem tot5108 : totK PA10K2 A10K2.t5108 = [0, 0, 351748226788, 1573684363875, 2191102094241, 833492070953, 54479702532, 0, 0, 0] := by
  decide +kernel

theorem rows5109 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5109 = true := by
  decide +kernel

theorem tot5109 : totK PA10K2 A10K2.t5109 = [0, 309035082669, 1105941095428, 1591070385752, 1397682291881, 552692917597, 50889683698, 0, 0, 0] := by
  decide +kernel

theorem rows5110 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5110 = true := by
  decide +kernel

theorem tot5110 : totK PA10K2 A10K2.t5110 = [0, 490159822480, 1783417058472, 1908560614661, 549520129694, 32040661968, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5111 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5111 = true := by
  decide +kernel

theorem tot5111 : totK PA10K2 A10K2.t5111 = [0, 0, 679642828896, 2001995617481, 1594659038469, 383693999907, 25371180993, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
