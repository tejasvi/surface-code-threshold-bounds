import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14916 = true := by
  decide +kernel

theorem tot14916 : totK PD2M8K2 D2M8K2.t14916 = [0, 182252869939, 451365643939, 254114184981, 28502591063, 0, 0, 0] := by
  decide +kernel

theorem rows14917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14917 = true := by
  decide +kernel

theorem tot14917 : totK PD2M8K2 D2M8K2.t14917 = [0, 188632794406, 455472868357, 216530468409, 12310507219, 0, 0, 0] := by
  decide +kernel

theorem rows14918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14918 = true := by
  decide +kernel

theorem tot14918 : totK PD2M8K2 D2M8K2.t14918 = [0, 34021490145, 319912849255, 448121163953, 94292238881, 1164319620, 0, 0] := by
  decide +kernel

theorem rows14919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14919 = true := by
  decide +kernel

theorem tot14919 : totK PD2M8K2 D2M8K2.t14919 = [0, 18617230336, 272619288070, 473386668574, 121483020009, 4008488258, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
