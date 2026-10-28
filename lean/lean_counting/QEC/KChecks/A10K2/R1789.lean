import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7156 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7156 = true := by
  decide +kernel

theorem tot7156 : totK PA10K2 A10K2.t7156 = [0, 0, 0, 459893921114, 1784488492348, 1875917326090, 420631826733, 17680085359, 0, 0] := by
  decide +kernel

theorem rows7157 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7157 = true := by
  decide +kernel

theorem tot7157 : totK PA10K2 A10K2.t7157 = [0, 0, 115548944004, 280842248814, 828255623404, 1904309062616, 1169812084211, 185933668476, 5676195732, 0] := by
  decide +kernel

theorem rows7158 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7158 = true := by
  decide +kernel

theorem tot7158 : totK PA10K2 A10K2.t7158 = [0, 0, 530898193989, 1873972937421, 1922576796312, 519153542228, 31301336365, 0, 0, 0] := by
  decide +kernel

theorem rows7159 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7159 = true := by
  decide +kernel

theorem tot7159 : totK PA10K2 A10K2.t7159 = [0, 0, 160863886679, 1090123584942, 2113701524295, 1311650763971, 260132738839, 20058242317, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
