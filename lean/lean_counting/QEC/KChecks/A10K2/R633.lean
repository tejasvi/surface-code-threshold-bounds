import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2532 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2532 = true := by
  decide +kernel

theorem tot2532 : totK PA10K2 A10K2.t2532 = [0, 224689426326, 1337627356676, 2255082385810, 1214590302479, 151998798654, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2533 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2533 = true := by
  decide +kernel

theorem tot2533 : totK PA10K2 A10K2.t2533 = [0, 0, 410591904814, 1779474049981, 2168303276961, 680518768064, 41062513076, 0, 0, 0] := by
  decide +kernel

theorem rows2534 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2534 = true := by
  decide +kernel

theorem tot2534 : totK PA10K2 A10K2.t2534 = [0, 0, 459320463974, 1818131777851, 1899307313248, 484890059764, 26479096260, 0, 0, 0] := by
  decide +kernel

theorem rows2535 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2535 = true := by
  decide +kernel

theorem tot2535 : totK PA10K2 A10K2.t2535 = [0, 0, 274112056881, 1301013065331, 2055946498986, 1099785077287, 174865696846, 9729745405, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
