import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5232 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5232 = true := by
  decide +kernel

theorem tot5232 : totK PA10K2 A10K2.t5232 = [0, 0, 0, 0, 874740604724, 2277925525877, 1162073921522, 103210728899, 0, 0] := by
  decide +kernel

theorem rows5233 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5233 = true := by
  decide +kernel

theorem tot5233 : totK PA10K2 A10K2.t5233 = [0, 0, 0, 719901543799, 2024881805462, 1589075389763, 474034147713, 100307121741, 5528811039, 0] := by
  decide +kernel

theorem rows5234 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5234 = true := by
  decide +kernel

theorem tot5234 : totK PA10K2 A10K2.t5234 = [0, 0, 412800395519, 1276067372845, 1700859807453, 1210132571204, 359465362598, 29010686974, 0, 0] := by
  decide +kernel

theorem rows5235 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5235 = true := by
  decide +kernel

theorem tot5235 : totK PA10K2 A10K2.t5235 = [0, 0, 384291644692, 1745572541671, 2062710147770, 627660464102, 35698002757, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
