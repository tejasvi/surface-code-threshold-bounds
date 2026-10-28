import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4920 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4920 = true := by
  decide +kernel

theorem tot4920 : totK PA10K2 A10K2.t4920 = [0, 382674072533, 1778032507849, 2040010951261, 523704082176, 31889781550, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4921 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4921 = true := by
  decide +kernel

theorem tot4921 : totK PA10K2 A10K2.t4921 = [0, 0, 729375688727, 2153879897665, 1447957203645, 221771206512, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4922 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4922 = true := by
  decide +kernel

theorem tot4922 : totK PA10K2 A10K2.t4922 = [511706341673, 1871473457435, 1964413084808, 528148023486, 26428021069, 30401557407, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows4923 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4923 = true := by
  decide +kernel

theorem tot4923 : totK PA10K2 A10K2.t4923 = [262183094928, 1274098343581, 2089693558766, 1223794342548, 171065023223, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
