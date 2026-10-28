import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5156 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5156 = true := by
  decide +kernel

theorem tot5156 : totK PA10K2 A10K2.t5156 = [0, 0, 274889264427, 1168515909367, 1849307690779, 1154004691766, 228179536165, 6354482628, 0, 0] := by
  decide +kernel

theorem rows5157 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5157 = true := by
  decide +kernel

theorem tot5157 : totK PA10K2 A10K2.t5157 = [0, 0, 494063907808, 1801347621531, 2001906780551, 589670545532, 32770461231, 0, 0, 0] := by
  decide +kernel

theorem rows5158 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5158 = true := by
  decide +kernel

theorem tot5158 : totK PA10K2 A10K2.t5158 = [0, 0, 490584767793, 1813657823856, 1931303469908, 507299267118, 19117496088, 0, 0, 0] := by
  decide +kernel

theorem rows5159 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5159 = true := by
  decide +kernel

theorem tot5159 : totK PA10K2 A10K2.t5159 = [0, 0, 0, 634818858041, 2082658186628, 1591423387025, 324430265909, 25299471099, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
