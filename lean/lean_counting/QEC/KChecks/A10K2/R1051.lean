import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4204 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4204 = true := by
  decide +kernel

theorem tot4204 : totK PA10K2 A10K2.t4204 = [0, 218496733400, 1190576705985, 2044203408773, 1254598255546, 221085315741, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows4205 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4205 = true := by
  decide +kernel

theorem tot4205 : totK PA10K2 A10K2.t4205 = [0, 339842317673, 1417042274040, 2051168867542, 1008841124591, 112257105785, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4206 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4206 = true := by
  decide +kernel

theorem tot4206 : totK PA10K2 A10K2.t4206 = [0, 413295823201, 1743777732480, 2068382887446, 699515105980, 57288305314, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4207 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4207 = true := by
  decide +kernel

theorem tot4207 : totK PA10K2 A10K2.t4207 = [0, 0, 496367017033, 1811973526928, 1883817154276, 491096215642, 31452573850, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
