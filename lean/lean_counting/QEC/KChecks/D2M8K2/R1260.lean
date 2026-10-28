import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5040 = true := by
  decide +kernel

theorem tot5040 : totK PD2M8K2 D2M8K2.t5040 = [0, 180111024545, 476592094850, 244257587443, 16716523752, 0, 0, 0] := by
  decide +kernel

theorem rows5041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5041 = true := by
  decide +kernel

theorem tot5041 : totK PD2M8K2 D2M8K2.t5041 = [0, 81130238399, 364152003440, 361323950166, 99602019500, 13132762340, 0, 0] := by
  decide +kernel

theorem rows5042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5042 = true := by
  decide +kernel

theorem tot5042 : totK PD2M8K2 D2M8K2.t5042 = [0, 0, 168618234052, 453750337832, 267507859384, 16242313759, 0, 0] := by
  decide +kernel

theorem rows5043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5043 = true := by
  decide +kernel

theorem tot5043 : totK PD2M8K2 D2M8K2.t5043 = [0, 49080275478, 225910497232, 429156359623, 191437265977, 8187419287, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
