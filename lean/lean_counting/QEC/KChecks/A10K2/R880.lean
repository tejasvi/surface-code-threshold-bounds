import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3520 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3520 = true := by
  decide +kernel

theorem tot3520 : totK PA10K2 A10K2.t3520 = [0, 0, 0, 0, 737409569335, 2136769131449, 1475265385901, 236072970520, 6354482628, 0] := by
  decide +kernel

theorem rows3521 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3521 = true := by
  decide +kernel

theorem tot3521 : totK PA10K2 A10K2.t3521 = [0, 0, 0, 0, 671942844875, 2136262449070, 1602093802924, 249599473093, 6354603908, 0] := by
  decide +kernel

theorem rows3522 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3522 = true := by
  decide +kernel

theorem tot3522 : totK PA10K2 A10K2.t3522 = [0, 0, 0, 0, 556578936280, 1877171356269, 1762215136504, 450552967765, 31690783744, 0] := by
  decide +kernel

theorem rows3523 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3523 = true := by
  decide +kernel

theorem tot3523 : totK PA10K2 A10K2.t3523 = [0, 0, 0, 0, 575411039613, 1854697264129, 1672902153010, 421466684429, 30874154442, 0] := by
  decide +kernel

end QECKChecks.A10K2
