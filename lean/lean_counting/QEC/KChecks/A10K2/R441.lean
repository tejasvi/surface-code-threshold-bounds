import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1764 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1764 = true := by
  decide +kernel

theorem tot1764 : totK PA10K2 A10K2.t1764 = [0, 0, 434482428232, 1756646918748, 1982536400029, 560516934079, 32040661968, 0, 0, 0] := by
  decide +kernel

theorem rows1765 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1765 = true := by
  decide +kernel

theorem tot1765 : totK PA10K2 A10K2.t1765 = [0, 0, 163480576023, 1065978538862, 1997607831424, 1292029248402, 261720179718, 20070762815, 0, 0] := by
  decide +kernel

theorem rows1766 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1766 = true := by
  decide +kernel

theorem tot1766 : totK PA10K2 A10K2.t1766 = [0, 0, 174965678288, 898183920565, 1883837233555, 1481630934864, 299358471392, 10760911071, 0, 0] := by
  decide +kernel

theorem rows1767 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1767 = true := by
  decide +kernel

theorem tot1767 : totK PA10K2 A10K2.t1767 = [0, 0, 438062998795, 1680077757452, 1892033353593, 639038812874, 52230035883, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
