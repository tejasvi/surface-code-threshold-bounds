import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2760 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2760 = true := by
  decide +kernel

theorem tot2760 : totK PA10K2 A10K2.t2760 = [527099952449, 1923644890480, 1965251260259, 502389000589, 13149912228, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2761 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2761 = true := by
  decide +kernel

theorem tot2761 : totK PA10K2 A10K2.t2761 = [0, 663889390157, 2018430431106, 1668143921304, 397995866641, 25371180993, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2762 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2762 = true := by
  decide +kernel

theorem tot2762 : totK PA10K2 A10K2.t2762 = [291919316456, 1213980041155, 1867410247432, 1245840221980, 214682274080, 5460492893, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2763 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2763 = true := by
  decide +kernel

theorem tot2763 : totK PA10K2 A10K2.t2763 = [268561015556, 1479392846547, 2211249319717, 808665508010, 45435019845, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
