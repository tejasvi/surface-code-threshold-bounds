import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6172 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6172 = true := by
  decide +kernel

theorem tot6172 : totK PA10K2 A10K2.t6172 = [0, 0, 0, 571703632186, 1892316755399, 1792537563248, 433938871927, 18779842006, 0, 0] := by
  decide +kernel

theorem rows6173 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6173 = true := by
  decide +kernel

theorem tot6173 : totK PA10K2 A10K2.t6173 = [0, 0, 0, 516701292084, 1835869590479, 1796211480538, 421275605202, 30259048844, 0, 0] := by
  decide +kernel

theorem rows6174 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6174 = true := by
  decide +kernel

theorem tot6174 : totK PA10K2 A10K2.t6174 = [0, 0, 0, 111369051068, 1277398086949, 2211114880750, 798048361307, 63645606988, 0, 0] := by
  decide +kernel

theorem rows6175 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6175 = true := by
  decide +kernel

theorem tot6175 : totK PA10K2 A10K2.t6175 = [0, 0, 414273244854, 1377095545765, 1431642380880, 850827586120, 550780106372, 128522833411, 5676195732, 0] := by
  decide +kernel

end QECKChecks.A10K2
