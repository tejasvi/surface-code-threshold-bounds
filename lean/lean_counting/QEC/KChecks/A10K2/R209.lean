import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows836 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t836 = true := by
  decide +kernel

theorem tot836 : totK PA10K2 A10K2.t836 = [0, 0, 648583678511, 2169458804534, 1899313504459, 350607898966, 6962742351, 0, 0, 0] := by
  decide +kernel

theorem rows837 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t837 = true := by
  decide +kernel

theorem tot837 : totK PA10K2 A10K2.t837 = [0, 0, 382248857563, 1592752961602, 2053768896347, 776820445619, 60578866985, 0, 0, 0] := by
  decide +kernel

theorem rows838 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t838 = true := by
  decide +kernel

theorem tot838 : totK PA10K2 A10K2.t838 = [0, 0, 521886810794, 1939842915225, 1921753942949, 431067726638, 12917769548, 0, 0, 0] := by
  decide +kernel

theorem rows839 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t839 = true := by
  decide +kernel

theorem tot839 : totK PA10K2 A10K2.t839 = [0, 0, 0, 570022873466, 1938859935209, 1696304105247, 411830910087, 25565504801, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
