import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1952 = true := by
  decide +kernel

theorem tot1952 : totK PD2M8K2 D2M8K2.t1952 = [0, 14935442529, 190880919006, 462400810680, 196367817773, 12052611869, 0, 0] := by
  decide +kernel

theorem rows1953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1953 = true := by
  decide +kernel

theorem tot1953 : totK PD2M8K2 D2M8K2.t1953 = [0, 191682794346, 460069055829, 217657267593, 18175578451, 0, 0, 0] := by
  decide +kernel

theorem rows1954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1954 = true := by
  decide +kernel

theorem tot1954 : totK PD2M8K2 D2M8K2.t1954 = [0, 187853370570, 452113595255, 232329910471, 17104814242, 0, 0, 0] := by
  decide +kernel

theorem rows1955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1955 = true := by
  decide +kernel

theorem tot1955 : totK PD2M8K2 D2M8K2.t1955 = [0, 11585800147, 314064399315, 464691771388, 88039755999, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
