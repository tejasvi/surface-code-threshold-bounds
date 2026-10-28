import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15856 = true := by
  decide +kernel

theorem tot15856 : totK PD2M8K2 D2M8K2.t15856 = [0, 172571630672, 462564196758, 249172861253, 17125878239, 0, 0, 0] := by
  decide +kernel

theorem rows15857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15857 = true := by
  decide +kernel

theorem tot15857 : totK PD2M8K2 D2M8K2.t15857 = [0, 0, 174757848324, 450144991863, 257128103410, 23785759959, 0, 0] := by
  decide +kernel

theorem rows15858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15858 = true := by
  decide +kernel

theorem tot15858 : totK PD2M8K2 D2M8K2.t15858 = [0, 0, 208352663976, 486587196441, 191277570372, 5430665091, 0, 0] := by
  decide +kernel

theorem rows15859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15859 = true := by
  decide +kernel

theorem tot15859 : totK PD2M8K2 D2M8K2.t15859 = [0, 176600050142, 399284302049, 236436893051, 96091302926, 6775760191, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
