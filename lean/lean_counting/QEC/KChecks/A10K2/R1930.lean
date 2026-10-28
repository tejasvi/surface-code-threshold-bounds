import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7720 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7720 = true := by
  decide +kernel

theorem tot7720 : totK PA10K2 A10K2.t7720 = [0, 0, 0, 40274886064, 1197714346186, 2357291979001, 943342810091, 75537625571, 0, 0] := by
  decide +kernel

theorem rows7721 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7721 = true := by
  decide +kernel

theorem tot7721 : totK PA10K2 A10K2.t7721 = [0, 0, 406392106167, 1318351598682, 1362150456326, 898460087169, 634260271854, 154386751909, 6354482628, 0] := by
  decide +kernel

theorem rows7722 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7722 = true := by
  decide +kernel

theorem tot7722 : totK PA10K2 A10K2.t7722 = [0, 0, 370217742698, 1677483388991, 2147188765755, 815952031976, 71329326040, 0, 0, 0] := by
  decide +kernel

theorem rows7723 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7723 = true := by
  decide +kernel

theorem tot7723 : totK PA10K2 A10K2.t7723 = [0, 0, 111406325205, 898740171458, 2066205181064, 1521433030688, 338263475311, 13364899180, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
