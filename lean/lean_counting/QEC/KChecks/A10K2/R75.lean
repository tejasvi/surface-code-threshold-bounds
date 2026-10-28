import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows300 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t300 = true := by
  decide +kernel

theorem tot300 : totK PA10K2 A10K2.t300 = [0, 465640888961, 1646628009173, 1819301363078, 721847927189, 80959961132, 0, 0, 0, 0] := by
  decide +kernel

theorem rows301 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t301 = true := by
  decide +kernel

theorem tot301 : totK PA10K2 A10K2.t301 = [0, 293434943870, 1494680092603, 2137940940478, 783011799855, 45918807480, 0, 0, 0, 0] := by
  decide +kernel

theorem rows302 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t302 = true := by
  decide +kernel

theorem tot302 : totK PA10K2 A10K2.t302 = [0, 297392362862, 1150038222010, 1796952543515, 1214486416564, 235068694400, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows303 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t303 = true := by
  decide +kernel

theorem tot303 : totK PA10K2 A10K2.t303 = [0, 292846243945, 1530722851773, 2259402740879, 894543730911, 75702874438, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
