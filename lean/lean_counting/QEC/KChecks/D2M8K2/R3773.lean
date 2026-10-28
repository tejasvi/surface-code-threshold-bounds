import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15092 = true := by
  decide +kernel

theorem tot15092 : totK PD2M8K2 D2M8K2.t15092 = [0, 0, 191387802642, 460998740800, 211169545189, 12593797338, 0, 0] := by
  decide +kernel

theorem rows15093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15093 = true := by
  decide +kernel

theorem tot15093 : totK PD2M8K2 D2M8K2.t15093 = [0, 0, 194319947429, 498022777535, 203679582170, 4039418239, 0, 0] := by
  decide +kernel

theorem rows15094 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15094 = true := by
  decide +kernel

theorem tot15094 : totK PD2M8K2 D2M8K2.t15094 = [0, 0, 169853991036, 460441756148, 223228532825, 12367370283, 0, 0] := by
  decide +kernel

theorem rows15095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15095 = true := by
  decide +kernel

theorem tot15095 : totK PD2M8K2 D2M8K2.t15095 = [0, 0, 208154983800, 475491299040, 185679789291, 8969527614, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
