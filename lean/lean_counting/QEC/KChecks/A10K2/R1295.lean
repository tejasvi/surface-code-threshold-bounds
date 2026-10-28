import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5180 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5180 = true := by
  decide +kernel

theorem tot5180 : totK PA10K2 A10K2.t5180 = [0, 392279175903, 1537941082659, 2049551885115, 856268164671, 80551352373, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5181 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5181 = true := by
  decide +kernel

theorem tot5181 : totK PA10K2 A10K2.t5181 = [0, 321789752003, 1574470327016, 1974576731696, 662312154311, 53286883679, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5182 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5182 = true := by
  decide +kernel

theorem tot5182 : totK PA10K2 A10K2.t5182 = [0, 174216242201, 895101985149, 1899865528614, 1378119373902, 247980810997, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows5183 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5183 = true := by
  decide +kernel

theorem tot5183 : totK PA10K2 A10K2.t5183 = [0, 553932213841, 1976965802756, 1931352017585, 489725690128, 25584519718, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
