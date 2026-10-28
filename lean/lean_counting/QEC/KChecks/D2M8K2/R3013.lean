import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12052 = true := by
  decide +kernel

theorem tot12052 : totK PD2M8K2 D2M8K2.t12052 = [0, 0, 226643154096, 494338820597, 158112372623, 3724448267, 0, 0] := by
  decide +kernel

theorem rows12053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12053 = true := by
  decide +kernel

theorem tot12053 : totK PD2M8K2 D2M8K2.t12053 = [0, 0, 201794973173, 477900654129, 193499298995, 10127428633, 0, 0] := by
  decide +kernel

theorem rows12054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12054 = true := by
  decide +kernel

theorem tot12054 : totK PD2M8K2 D2M8K2.t12054 = [0, 0, 197540580691, 467862379697, 185119373467, 9503353481, 0, 0] := by
  decide +kernel

theorem rows12055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12055 = true := by
  decide +kernel

theorem tot12055 : totK PD2M8K2 D2M8K2.t12055 = [0, 0, 87881279390, 400092150633, 313871499278, 47192179014, 1310517177, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
