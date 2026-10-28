import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1828 = true := by
  decide +kernel

theorem tot1828 : totK PD2M8K2 D2M8K2.t1828 = [0, 0, 182097221416, 470906378540, 252552208259, 17838358835, 0, 0] := by
  decide +kernel

theorem rows1829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1829 = true := by
  decide +kernel

theorem tot1829 : totK PD2M8K2 D2M8K2.t1829 = [0, 0, 171653650330, 459816540034, 238167422872, 14964360782, 0, 0] := by
  decide +kernel

theorem rows1830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1830 = true := by
  decide +kernel

theorem tot1830 : totK PD2M8K2 D2M8K2.t1830 = [0, 0, 0, 290151134460, 481450142526, 117154339756, 4009909289, 0] := by
  decide +kernel

theorem rows1831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1831 = true := by
  decide +kernel

theorem tot1831 : totK PD2M8K2 D2M8K2.t1831 = [0, 0, 96716684966, 352438923855, 355963492272, 73061904788, 1149959346, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
